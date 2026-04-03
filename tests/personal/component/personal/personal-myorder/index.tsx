/*
 *@Date: 2022-01-05 10:20:33
 *@Description: 个人中心固定订单模块
 */
import React, { PureComponent } from 'react';
import { View, Text, TouchableOpacity, DeviceEventEmitter, Platform, Dimensions } from 'react-native';
import {
  WithTheme,
  componentautoscaling,
  t,
  SuitStyle as theme,
  CommonUtils,
  RouterUtils,
  screenSize as getScreenSize,
  itemExposeHoc,
  monitor,
  HttpService,
  Service as env,
  DarkStore,
  PlatformUtils,
  fontStore,
  FONT_MUTIPLE,
  LoginUtils,
  BBD_KEY,
} from '@hw-vmall/vrn-basic-comp';
import { SvgIcon, FastImageView } from '@hw-vmall/vrn-bussiness-comp';
import { urlData } from '../../../../../common/config/constants';
import OrderSchedule from '../order-schedule';
import dapReportList from './dapReportList';
import hmiReportList from './hmiReportList';
import Styles from './style';

interface Props {
  isLogin: any;
  width: any;
  height: any;
}
enum TemplatePlaceholder {
  h5ConfigRma = 'H5_CONFIG_RMA',
  bpClientWechatOrderSwitch = 'bp_client_wechat_order_switch',
  exchangeUrlSwitch = 'switch_to_rn_url',
}
class MyOrder extends PureComponent<any, any> {
  eventListener: any;
  cancelLoginListener: any;
  itemlist: any[] = [];
  width: number;
  linkFinished: any;
  apkGotourlMy: any;
  hmiSpanId: any; // begin埋点返回的数据，里面有spanId
  constructor(props: any) {
    super(props);
    this.state = {
      width: CommonUtils.getWindowSize('personal').screenWidth,
      height: CommonUtils.getWindowSize('personal').screenHeight,
      normalColor: theme.C17.color,
      normalCol: theme.C11.color,
      unpaidOrderCount: '', // 未支付订单
      unreceiptOrderCount: '', // 待收货
      rmaAppCount: '', // 退换货
      count: '', // 评价
      isShow: false,
      gotourl: '',
      exchangeUrl: `${env.wapDomain}member/rma/index`, // 退货换货跳转地址
      exchangeRnUrl: '',
      showApplet: '0', // 是否展示小程序
      isCommentNewStyle: false, // 待评价提示语新样式BBD开关
      isFinish: false,
    };
    this.linkFinished = true;
  }

  isApp = () => {
    return PlatformUtils.isApp();
  };
  isWeb = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return PlatformUtils.isPc(width);
  };
  isPad = () => {
    return getScreenSize(this.state.width) === 'medium';
  };

  isWap = () => {
    return getScreenSize(this.state.width) === 'small';
  };
  isPadH = () => {
    const sWidth = Platform.OS === 'web' ? Dimensions.get('window').width : this.state.width;
    const sHeight = Platform.OS === 'web' ? Dimensions.get('window').height : this.state.height;
    return sWidth >= sHeight;
  };
  async componentDidMount() {
    if (this.state.width !== CommonUtils.getWindowSize('personal').screenWidth) {
      this.setState({
        width: CommonUtils.getWindowSize('personal').screenWidth,
        height: CommonUtils.getWindowSize('personal').screenHeight,
      });
    }
    this.eventListener = LoginUtils.listenLoginStatus((isLogin: boolean) => {
      if (isLogin === false && this.linkFinished === false) {
        this.linkFinished = true;
        this.apkGotourlMy = '';
      }
    });
    this.cancelLoginListener = DeviceEventEmitter.addListener('NativeCallAction', (event: any) => {
      if (event && event.service === 'login' && event.action === 'loginOut' && !event.param?.isLogin) {
        this.linkFinished = true;
        this.apkGotourlMy = '';
      }
    });
    // 根据systemconfig配置情况，决定跳转APPServer还是Wapdomain
    this.getExchangeUrl();
  }

  async componentDidUpdate() {}

  componentWillUnmount() {
    this.eventListener?.remove();
    this.cancelLoginListener?.remove();
  }

  // 数据请求
  receiveRef = (ref) => {
    if (!ref) {
      return;
    }
    this.itemlist.push(ref);
  };

  // 渲染小程序二维码弹窗
  renderMpUidInfo(_styles) {
    return (
      <View style={[_styles.popUpWindow]}>
        <TouchableOpacity activeOpacity={1} style={[_styles.popUpWindowIcon]} onPress={this.onClose}>
          <SvgIcon iconName="cancel1" width="20" height="20" />
        </TouchableOpacity>
        <FastImageView imgStyle={[_styles.popUpWindowImage]} imgUri={urlData.popUpWindowImage} />
        <View style={[_styles.popUpWindowText]}>
          <Text style={[_styles.popUpWindowHeight]}>{t('bind')}</Text>
          <Text style={[_styles.popUpWindowHeight]}>
            {t('after_binding')}
            <Text style={{ color: '#ca141d' }}>{t('re_login')}</Text>
            {t('view_mp_orders')}
          </Text>
        </View>
        <TouchableOpacity activeOpacity={1} style={[_styles.popUpWindowButton]} onPress={this.onClose}>
          <Text style={[_styles.popUpWindowButtonText]}>{t('i_know')}</Text>
        </TouchableOpacity>
      </View>
    );
  }
  // 关闭弹窗
  onClose = () => {
    this.setState({
      isShow: !this.state.isShow,
    });
  };
  // 点击跳转
  _onclick = async (key: string) => {
    this.hmiSpanId = await hmiReportList.hmiClickOrder(this.props, 'begin', key);
    const { clickItem, isLogin } = this.props;
    this.setState({
      gotourl: this.switchClick(key),
    });
    this.apkGotourlMy = this.switchClick(key);
    if (isLogin) {
      const url = this.switchClick(key);
      if (key === 'ic_') {
        if (this.props.mpUid) {
          const gotoPageFunction = () => {
            RouterUtils.gotoPage(url);
          };
          CommonUtils.delayGotoPage(gotoPageFunction);
        } else {
          this.setState({
            isShow: !this.state.isShow,
          });
        }
        clickItem(key, url);
      } else {
        const gotoPageFunction = () => {
          RouterUtils.gotoPage(url);
        };
        CommonUtils.delayGotoPage(gotoPageFunction);
        clickItem(key, url);
      }
    } else {
      const url = 'vmall://com.vmall.client/home/login';
      if (this.isApp()) {
        this.eventListener = LoginUtils.listenLoginStatus((login: boolean) => {
          if (login === true && this.linkFinished === true) {
            this.linkFinished = false;
            RouterUtils.gotoPage(this.apkGotourlMy);
          }
        });
        RouterUtils.gotoPage(url);
        clickItem(key);
      } else {
        const path: string = document.location.href;
        if (key === 'ic_') {
          const loginUrl = `${env.webDomain}account/login?url=${encodeURIComponent(path)}`;
          const gotoPageFunction = () => {
            RouterUtils.gotoPage(loginUrl, false);
          };
          CommonUtils.delayGotoPage(gotoPageFunction);
        } else {
          const pageUrl = encodeURIComponent(this.switchClick(key));
          const loginUrl = this.isWeb()
            ? `${env.webDomain}account/login?url=${pageUrl}`
            : `${env.wapDomain}account/applogin?url=${pageUrl}`;
          clickItem(key);
          RouterUtils.gotoPage(loginUrl);
        }
      }
    }
    hmiReportList.hmiClickOrder(this.props, 'end', key, this.hmiSpanId);
  };

  switchClick = (key) => {
    let url: string;
    switch (key) {
      case 'ic5':
        // 待付款
        url = this.getUrl(
          `${env.wapDomain}member/order?tagId=unpaid`,
          `${env.webDomain}member/order?type=unpaid`,
          `${env.wapDomain}order/unpaid`,
        );

        return url;
      case 'ic3':
        // 待收货
        url = this.getUrl(
          `${env.wapDomain}member/order?tagId=unreceivce`,
          `${env.webDomain}member/order?type=send`,
          `${env.wapDomain}member/unreceiptOrder`,
        );
        return url;
      case 'ic4':
        // 待评价
        url = this.getUrl(
          `${env.wapDomain}member/evaluateOrder`,
          `${env.webDomain}member/order?type=nocomment`,
          `${env.wapDomain}member/evaluateOrder`,
        );
        return url;
      case 'ic1':
        // 退换/退款
        url = this.state.exchangeRnUrl
          ? this.getUrl(
              `${env.wapDomain}${this.state.exchangeRnUrl}`,
              `${env.webDomain}${this.state.exchangeRnUrl}`,
              `${env.wapDomain}${this.state.exchangeRnUrl}`,
            )
          : this.getUrl(
              this.state.exchangeUrl,
              `${env.webDomain}member/exchange`,
              `${env.wapDomain}member/rma/index?activeIndex=1`,
            );
        return url;
      case 'ic_':
        // 小程序
        url = `${env.webDomain}member/orderWeChat`;
        return url;
      case 'ic2':
        // 回收单
        url = this.isWeb() ? `${env.webDomain}member/recycle/index` : `${env.wapDomain}member/recycleall/index`;
        return url;
      case 'all':
        // 全部订单
        url = this.getUrl(
          `${env.wapDomain}member/order?tagId=all`,
          `${env.webDomain}member/order?tagId=all`,
          `${env.wapDomain}member/order`,
        );
        return url;
      default:
        break;
    }
  };

  getUrl(appUrl, webUrl, otherUrl) {
    if (this.isApp()) {
      return appUrl;
    } else if (this.isWeb()) {
      return webUrl;
    } else {
      return otherUrl;
    }
  }

  // 退换/退款跳转地址/是否展示小程序入口
  getExchangeUrl = () => {
    return new Promise((resolve) => {
      HttpService.querySystemConfig(
        `['${TemplatePlaceholder.h5ConfigRma}','${TemplatePlaceholder.bpClientWechatOrderSwitch}','${BBD_KEY.COMMENT_FEATURE_SHOW_POINTS}','${TemplatePlaceholder.exchangeUrlSwitch}']`,
      )
        .then((res) => {
          if (res.systemConfigInfos) {
            const rmaUrl =
              res.systemConfigInfos[`${TemplatePlaceholder.h5ConfigRma}`]?.systemConfigValue === '1'
                ? `${env.wapDomain}member/rma/index?activeIndex=1`
                : `${env.wapDomain}member/rma/index`;
            const rmaRnUrl =
              res.systemConfigInfos[`${TemplatePlaceholder.exchangeUrlSwitch}`]?.systemConfigValue === '1'
                ? 'sc/exchange/index.html'
                : '';
            this.setState({
              isCommentNewStyle:
                res.systemConfigInfos[`${BBD_KEY.COMMENT_FEATURE_SHOW_POINTS}`]?.systemConfigValue === '1',
              exchangeUrl: res.systemConfigInfos[`${TemplatePlaceholder.h5ConfigRma}`]
                ? rmaUrl
                : `${env.wapDomain}member/rma/index`,
              showApplet: !res.systemConfigInfos[`${TemplatePlaceholder.bpClientWechatOrderSwitch}`]
                ? '0'
                : res.systemConfigInfos[`${TemplatePlaceholder.bpClientWechatOrderSwitch}`].systemConfigValue,
              exchangeRnUrl: rmaRnUrl,
            });
            resolve({});
          }
        })
        .finally(() => {
          this.setState({ isFinish: true });
        });
    });
  };

  // 保留N位小数，默认两位
  fixedNum(val: number | string, n = 2) {
    if (val === 0) {
      return Number(val).toFixed(n);
    } else if (val > 99) {
      return '99+';
    } else {
      return val;
    }
  }

  initWidth = (width) => {
    if (this.state.width !== width) {
      this.setState({
        width: width,
      });
    }
  };
  render() {
    const {
      unpaidOrderCount, // 未支付订单
      unreceiptOrderCount,
      rmaAppCount,
      count,
      isLogin,
      latestOrderLogList,
    } = this.props;
    const { normalColor, normalCol, isCommentNewStyle, width, isFinish } = this.state;
    const isDarkTheme = DarkStore.darkBool;
    const supportPlatform = PlatformUtils.isApp() || PlatformUtils.isWap(width);
    const isNewStyle = supportPlatform && isCommentNewStyle;
    const evaluteText = isNewStyle ? t('evaluteGift') : this.fixedNum(count);
    const itemWidth = fontStore.fontMutiple > FONT_MUTIPLE.FONT_LEVEL_ONE ? 103 : 55;
    // 图标宽度
    const iconWidth = this.isWeb() ? 48 : 40;
    // 角标左右间距
    const markStyle: any = {
      paddingLeft: 6,
      paddingRight: 6,
    };
    const itemStyle: any = {
      width: this.isWeb() ? (1200 - 48) / 6 : itemWidth,
    };
    const iconCenter: any = {
      alignItems: 'center',
      justifyContent: 'center',
    };
    const itemBoxWidth = (this.state.width - 16 - 32) / 5;
    const bigFontMarkStyle: any = {
      borderRadius: 16,
      backgroundColor: '#CE0E2D',
      height: 16,
      paddingTop: 1,
      position: 'absolute',
      top: -3,
      left: 55,
    };
    const bigFontBoxStyle: any = {
      alignItems: 'center',
      justifyContent: 'center',
      width: itemWidth,
    };
    const commonParams = {
      bigFontBoxStyle,
      isLogin,
      unpaidOrderCount,
      bigFontMarkStyle,
      markStyle,
      iconWidth,
      isDarkTheme,
      normalColor,
      normalCol,
      count,
      isFinish,
      evaluteText,
      isNewStyle,
      rmaAppCount,
      iconCenter,
      itemStyle,
      unreceiptOrderCount,
      itemBoxWidth,
    };
    return (
      <WithTheme themeStyles={Styles}>
        {(_styles, theme: any, width: number) => {
          this.initWidth(width);
          const styleContent = this.getStyleContent(_styles);
          const size = getScreenSize(width);
          const boxMargin = size === 'small' ? 16 : 24;
          const SwiperWidth = width - boxMargin * 2 - 24;
          return (
            <View
              style={[
                {
                  width: '100%',
                },
                _styles.containerPad,
              ]}
            >
              <TouchableOpacity
                style={_styles.title}
                activeOpacity={1}
                onPress={() => {
                  this._onclick('all');
                }}
              >
                <Text style={[this.isWeb() ? _styles.titleLeftWeb : _styles.titleLeft]}>{t('my_orders')}</Text>
                {this.renderAllOrder(_styles, isDarkTheme)}
              </TouchableOpacity>
              {fontStore.fontMutiple > FONT_MUTIPLE.FONT_LEVEL_ONE ? (
                <>
                  <View style={[_styles.svgStyle]}>
                    {this.renderPedingPaymentForBigTxt(commonParams, _styles, styleContent)}
                    {this.renderToBeReceivedForBigTxt(commonParams, _styles, styleContent)}
                    {this.renderToBeEvaluatedForBigTxt(commonParams, _styles, styleContent)}
                    {this.renderReturnRefundForBigTxt(commonParams, _styles, styleContent)}
                    {this.renderRecyclingOrderForBigTxt(commonParams, _styles, styleContent)}
                  </View>
                </>
              ) : (
                <View style={[_styles.svgStyle]}>
                  {this.renderPedingPayment(commonParams, _styles, styleContent)}
                  {this.renderToBeReceived(commonParams, _styles, styleContent)}
                  {this.renderToBeEvaluated(commonParams, _styles, styleContent)}
                  {this.renderReturnRefundFor(commonParams, _styles, styleContent)}
                  {this.isWeb() ? (
                    <>
                      {this.state.showApplet === '1' ? (
                        <TouchableOpacity
                          activeOpacity={1}
                          onPress={() => this._onclick('ic_')}
                          ref={this.receiveRef}
                          style={iconCenter}
                        >
                          <SvgIcon
                            iconName={'ic_'}
                            width={iconWidth}
                            height={iconWidth}
                            normalCol={isDarkTheme ? normalColor : normalCol}
                          />
                          <View style={itemStyle}>
                            <Text style={styleContent} numberOfLines={2}>
                              {t('applet')}
                            </Text>
                          </View>
                        </TouchableOpacity>
                      ) : null}
                    </>
                  ) : null}
                  <TouchableOpacity
                    activeOpacity={1}
                    onPress={() => this._onclick('ic2')}
                    ref={this.receiveRef}
                    style={iconCenter}
                  >
                    <SvgIcon
                      iconName={'ic_2'}
                      width={iconWidth}
                      height={iconWidth}
                      normalCol={isDarkTheme ? normalColor : normalCol}
                    />
                    <View style={itemStyle}>
                      <Text style={styleContent} numberOfLines={2}>
                        {t('recycling_order')}
                      </Text>
                    </View>
                  </TouchableOpacity>
                </View>
              )}
              {!this.isWeb() && latestOrderLogList?.length ? (
                <OrderSchedule swiperWidth={SwiperWidth} latestOrderLogList={latestOrderLogList} />
              ) : null}
              {this.isWeb() ? (
                <View
                  style={[
                    this.state.isShow ? _styles.page : _styles.hide,
                    // eslint-disable-next-line react-native/no-inline-styles
                    {
                      alignItems: 'center',
                      width: '100%',
                      top: -200,
                    },
                  ]}
                >
                  {this.renderMpUidInfo(_styles)}
                </View>
              ) : null}
            </View>
          );
        }}
      </WithTheme>
    );
  }

  private renderReturnRefundFor(commonParams: any, _styles: any, styleContent: any) {
    const { iconWidth, isDarkTheme, normalColor, rmaAppCount, isLogin, markStyle, iconCenter, itemStyle, normalCol } =
      commonParams;
    return (
      <TouchableOpacity activeOpacity={1} onPress={() => this._onclick('ic1')} ref={this.receiveRef} style={iconCenter}>
        {isLogin && rmaAppCount > 0 ? (
          <View style={[_styles.mark, rmaAppCount > 9 ? markStyle : { width: 16 }]}>
            <Text style={[_styles.markText]}>{this.fixedNum(rmaAppCount)}</Text>
          </View>
        ) : null}
        <SvgIcon
          height={iconWidth}
          width={iconWidth}
          iconName={'ic_1'}
          normalCol={isDarkTheme ? normalColor : normalCol}
        />
        <View style={itemStyle}>
          <Text style={styleContent} numberOfLines={2}>
            {t('return_refund')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  }

  private renderToBeEvaluated(commonParams: any, _styles: any, styleContent: any) {
    const {
      iconWidth,
      isDarkTheme,
      normalColor,
      isFinish,
      count,
      isNewStyle,
      evaluteText,
      isLogin,
      markStyle,
      iconCenter,
      itemStyle,
      normalCol,
    } = commonParams;
    const newStyle = isNewStyle ? { paddingHorizontal: 2 } : markStyle;
    return (
      <TouchableOpacity activeOpacity={1} onPress={() => this._onclick('ic4')} ref={this.receiveRef} style={iconCenter}>
        {isLogin && count > 0 && isFinish ? (
          <View style={[count > 9 ? newStyle : { width: 16 }, isNewStyle ? _styles.evaluteGift : _styles.mark]}>
            <Text style={[_styles.markText]}>{evaluteText}</Text>
          </View>
        ) : null}
        <SvgIcon
          width={iconWidth}
          iconName={'ic_4'}
          height={iconWidth}
          normalCol={isDarkTheme ? normalColor : normalCol}
        />
        <View style={itemStyle}>
          <Text style={styleContent} numberOfLines={2}>
            {t('to_be_evaluated')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  }

  private renderToBeReceived(commonParams: any, _styles: any, styleContent: any) {
    const {
      iconWidth,
      isDarkTheme,
      normalColor,
      unreceiptOrderCount,
      isLogin,
      markStyle,
      iconCenter,
      itemStyle,
      normalCol,
    } = commonParams;
    return (
      <TouchableOpacity activeOpacity={1} onPress={() => this._onclick('ic3')} ref={this.receiveRef} style={iconCenter}>
        {isLogin && unreceiptOrderCount > 0 ? (
          <View style={[_styles.mark, unreceiptOrderCount > 9 ? markStyle : { width: 16 }]}>
            <Text style={[_styles.markText]}>{this.fixedNum(unreceiptOrderCount)}</Text>
          </View>
        ) : null}
        <SvgIcon
          iconName={'ic_3'}
          width={iconWidth}
          height={iconWidth}
          normalCol={isDarkTheme ? normalColor : normalCol}
        />
        <View style={itemStyle}>
          <Text style={styleContent} numberOfLines={2}>
            {t('to_be_received')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  }

  private renderPedingPayment(commonParams: any, _styles: any, styleContent: any) {
    const {
      iconWidth,
      isDarkTheme,
      normalColor,
      unpaidOrderCount,
      isLogin,
      markStyle,
      iconCenter,
      itemStyle,
      normalCol,
    } = commonParams;
    return (
      <TouchableOpacity activeOpacity={1} onPress={() => this._onclick('ic5')} ref={this.receiveRef} style={iconCenter}>
        {isLogin && unpaidOrderCount > 0 ? (
          <View style={[_styles.mark, unpaidOrderCount > 9 ? markStyle : { width: 16 }]}>
            <Text style={[_styles.markText]}>{this.fixedNum(unpaidOrderCount)}</Text>
          </View>
        ) : null}
        <SvgIcon
          iconName={'ic_5'}
          width={iconWidth}
          height={iconWidth}
          normalCol={isDarkTheme ? normalColor : normalCol}
        />
        <View style={itemStyle}>
          <Text style={styleContent} numberOfLines={2}>
            {t('peding_payment')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  }

  private renderRecyclingOrderForBigTxt(commonParams: any, _styles: any, styleContent: any) {
    const { bigFontBoxStyle, iconWidth, isDarkTheme, normalColor, normalCol } = commonParams;
    return (
      <TouchableOpacity
        activeOpacity={1}
        onPress={() => this._onclick('ic2')}
        ref={this.receiveRef}
        style={bigFontBoxStyle}
      >
        <SvgIcon
          iconName={'ic_2'}
          width={iconWidth}
          height={iconWidth}
          normalCol={isDarkTheme ? normalColor : normalCol}
        />
        <View>
          <Text style={styleContent} numberOfLines={2}>
            {t('recycling_order')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  }

  private renderReturnRefundForBigTxt(commonParams: any, _styles: any, styleContent: any) {
    const {
      bigFontBoxStyle,
      isLogin,
      bigFontMarkStyle,
      markStyle,
      rmaAppCount,
      iconWidth,
      isDarkTheme,
      normalColor,
      normalCol,
      itemBoxWidth,
    } = commonParams;
    return (
      <TouchableOpacity
        activeOpacity={1}
        onPress={() => this._onclick('ic1')}
        ref={this.receiveRef}
        style={bigFontBoxStyle}
      >
        {isLogin && rmaAppCount > 0 ? (
          <View style={[bigFontMarkStyle, rmaAppCount > 9 ? markStyle : { width: 16 }]}>
            <Text style={[_styles.markText]}>{this.fixedNum(rmaAppCount)}</Text>
          </View>
        ) : null}
        <SvgIcon
          iconName={'ic_1'}
          width={iconWidth}
          height={iconWidth}
          normalCol={isDarkTheme ? normalColor : normalCol}
        />
        <View style={{ width: itemBoxWidth }}>
          <Text style={styleContent} numberOfLines={2}>
            {t('return_refund')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  }

  private renderToBeEvaluatedForBigTxt(commonParams: any, _styles: any, styleContent: any) {
    const {
      bigFontBoxStyle,
      isLogin,
      count,
      isFinish,
      isNewStyle,
      evaluteText,
      bigFontMarkStyle,
      markStyle,
      iconWidth,
      isDarkTheme,
      normalColor,
      normalCol,
    } = commonParams;
    return (
      <TouchableOpacity
        activeOpacity={1}
        onPress={() => this._onclick('ic4')}
        ref={this.receiveRef}
        style={bigFontBoxStyle}
      >
        {isLogin && count > 0 && isFinish ? (
          <View style={[count > 9 ? markStyle : { width: 16 }, isNewStyle ? _styles.evaluteGift : bigFontMarkStyle]}>
            <Text style={[_styles.markText]}>{evaluteText}</Text>
          </View>
        ) : null}
        <SvgIcon
          iconName={'ic_4'}
          width={iconWidth}
          height={iconWidth}
          normalCol={isDarkTheme ? normalColor : normalCol}
        />
        <View>
          <Text style={styleContent} numberOfLines={2}>
            {t('to_be_evaluated')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  }

  private renderToBeReceivedForBigTxt(commonParams: any, _styles: any, styleContent: any) {
    const {
      bigFontBoxStyle,
      isLogin,
      unreceiptOrderCount,
      bigFontMarkStyle,
      markStyle,
      iconWidth,
      isDarkTheme,
      normalColor,
      normalCol,
    } = commonParams;
    return (
      <TouchableOpacity
        activeOpacity={1}
        onPress={() => this._onclick('ic3')}
        ref={this.receiveRef}
        style={bigFontBoxStyle}
      >
        {isLogin && unreceiptOrderCount > 0 ? (
          <View style={[bigFontMarkStyle, unreceiptOrderCount > 9 ? markStyle : { width: 16 }]}>
            <Text style={[_styles.markText]}>{this.fixedNum(unreceiptOrderCount)}</Text>
          </View>
        ) : null}
        <SvgIcon
          width={iconWidth}
          height={iconWidth}
          iconName={'ic_3'}
          normalCol={isDarkTheme ? normalColor : normalCol}
        />
        <View>
          <Text style={styleContent} numberOfLines={2}>
            {t('to_be_received')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  }

  private renderPedingPaymentForBigTxt(commonParams: any, _styles: any, styleContent: any) {
    const {
      bigFontBoxStyle,
      isLogin,
      unpaidOrderCount,
      bigFontMarkStyle,
      markStyle,
      iconWidth,
      isDarkTheme,
      normalColor,
      normalCol,
    } = commonParams;
    return (
      <TouchableOpacity
        activeOpacity={1}
        onPress={() => this._onclick('ic5')}
        ref={this.receiveRef}
        style={bigFontBoxStyle}
      >
        {isLogin && unpaidOrderCount > 0 ? (
          <View style={[bigFontMarkStyle, unpaidOrderCount > 9 ? markStyle : { width: 16 }]}>
            <Text style={[_styles.markText]}>{this.fixedNum(unpaidOrderCount)}</Text>
          </View>
        ) : null}
        <SvgIcon
          height={iconWidth}
          iconName={'ic_5'}
          width={iconWidth}
          normalCol={isDarkTheme ? normalColor : normalCol}
        />
        <View>
          <Text style={styleContent} numberOfLines={2}>
            {t('peding_payment')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  }

  private renderAllOrder(_styles: any, isDarkTheme: boolean) {
    return (
      <TouchableOpacity
        activeOpacity={1}
        onPress={() => {
          this._onclick('all');
        }}
        style={[
          fontStore.fontMutiple > FONT_MUTIPLE.FONT_LEVEL_ONE ? _styles.titleRightScale : _styles.titleRight,
          PlatformUtils.isHarmony() && { alignItems: 'center', paddingRight: 12 },
        ]}
      >
        <Text style={[fontStore.fontMutiple > FONT_MUTIPLE.FONT_LEVEL_ONE ? _styles.allScale : _styles.all]}>
          {t('all_orders')}
        </Text>
        <View
          style={{
            marginTop: fontStore.fontMutiple > FONT_MUTIPLE.FONT_LEVEL_ONE || PlatformUtils.isHarmony() ? 0 : 2,
            marginRight: PlatformUtils.isHarmony() ? -12 : 0,
            flexShrink: 0,
          }}
        >
          <SvgIcon
            iconName="Webarrow"
            width="12"
            height="24"
            normalCol={this.isWeb() ? 'rgba(0,0,0,0.90)' : 'rgba(0,0,0,0.20)'}
            viewBox={'0 0 512 1024'}
          />
        </View>
      </TouchableOpacity>
    );
  }

  private getStyleContent(_styles: any) {
    return this.isWeb() ? _styles.contentWeb : _styles.content;
  }
}
export default componentautoscaling(monitor(dapReportList)(itemExposeHoc(MyOrder)));
