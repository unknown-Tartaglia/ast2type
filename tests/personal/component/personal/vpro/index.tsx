/* eslint-disable react-native/no-inline-styles */
import {
  CommonUtils,
  itemExposeHoc,
  monitor,
  PlatformUtils,
  RouterUtils,
  WithTheme,
  t,
  DarkStore,
  ScreenUtils,
  SuitStyle,
} from '@hw-vmall/vrn-basic-comp';
import {
  ImageBackground as RNImageBackground,
  SvgIcon,
  FastImageView,
} from '@hw-vmall/vrn-bussiness-comp';
import React, { Component } from 'react';
import { vMemberType } from './prop';
import dapReportList from './dapReportList';
import Styles from './style/index';
import ImgArray from '../../../../../assets/ImgArray';
import { TouchableOpacity, View, Text } from 'react-native';
import _ from 'lodash';
import LinearGradient from 'react-native-linear-gradient';
import { getCardHeight } from '../../../utils/util';
class VMember extends Component<vMemberType, any> {
  constructor(props) {
    super(props);
  }
  getSize = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    return width;
  };

  getBlockWidth() {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    const paddingWidth = ScreenUtils.isMedium(this.getSize()) ? 48 : 32;
    return width - paddingWidth;
  }

  // 埋点处理
  dapReportClickData = (
    index: string,
    url: string,
    name: string,
    isVpro: string,
  ) => {
    const { clickItem } = this.props;
    let actionCode = ScreenUtils.isLarge(this.getSize()) ? '310000101' : '210000101';
    actionCode = PlatformUtils.isApp() ? '110000101' : actionCode;
    clickItem(actionCode, url, index, name, isVpro);
  };

  handlePress = (url: string) => {
    RouterUtils.gotoPage(url);
  };

  // n单返现逻辑
  getCashBack() {
    const { vproList } = this.props;
    const item = PlatformUtils.isApp()
      ? vproList?.configInfo && JSON.parse(vproList?.configInfo)
      : vproList;
    return item?.benefitDescSubTitle || '';
  }

  // “立即开通”跳转
  onVProGuideClick = () => {
    const { vproList } = this.props;
    const item = PlatformUtils.isApp()
      ? vproList?.configInfo && JSON.parse(vproList?.configInfo)
      : vproList;
    const url = PlatformUtils.isApp() ? item.openBtnAppLink : item.openBtnwapLink;
    this.dapReportClickData('10', url, '10', '0');
    RouterUtils.gotoPage(url);
  };

  renderVMember = (_styles, theme, isDarkTheme) => {
    const { vproList } = this.props;
    const item = this.getItem(vproList);
    const cashBack = this.getCashBack();
    const cashUrl = this.getCashUrl(item);
    const memberUrl = this.getMemberUrl(item);
    const themeSuit: any = SuitStyle;
    const memberIcon = this.getMemberIcon(isDarkTheme, item);
    const nOrderIcon = this.getOrderIcon(isDarkTheme, item);
    const showNOrderIcon = item?.showNOrderCashbackSetting === '2' && nOrderIcon;
    const showMemberIcon = item?.showMemberStoreSetting === '2' && memberIcon;
    const showNOrderText =
      item?.showNOrderCashbackSetting === '1' && item.nOrderCashback;
      const showMemberText =
      item?.showMemberStoreSetting === '1' && item.memberStore;
    const showMoreMemberInfoParams = {
      showMemberIcon,
      memberUrl,
      showMemberText,
      themeSuit,
      item,
      memberIcon,
    };
    return (
      <>
        <TouchableOpacity
          style={[
            ScreenUtils.isMedium(this.getSize())
              ? _styles.padBlock
              : _styles.logBlock,
            ScreenUtils.isMedium(this.getSize()) && PlatformUtils.isApp()
              ? {}
              : { width: this.getBlockWidth() / 2 },
            {
              paddingTop: showNOrderIcon ? 6 : 10,
            },
          ]}
          onPress={() => {
            this.dapReportClickData('11', cashUrl, '11', '1');
            this.handlePress(cashUrl);
          }}
        >
          <View style={_styles.leftBlock}>
            {showNOrderText ? (
              <Text
                style={[
                  _styles.textTitle,
                  {
                    color: themeSuit.C71.color,
                  },
                ]}
              >
                {_.truncate(item.nOrderCashback, {
                  length: 2,
                  omission: '',
                })}
              </Text>
            ) : null}
            {showNOrderIcon ? (
              <FastImageView
                imgUri={nOrderIcon}
                imgStyle={_styles.logoImg}
                resizeMode={'cover'}
              />
            ) : null}
            <Text
              style={[
                _styles.logoTitle,
                {
                  color: themeSuit.C71.color,
                  marginLeft: showNOrderIcon ? 2 : 0,
                },
              ]}
            >
              {_.truncate(item?.nOrderCashbackTitle, {
                length: 5,
                omission: '',
              })}
            </Text>
            <View style={{ paddingTop: PlatformUtils.isAndroid() || PlatformUtils.isHarmony() ? 1 : 0 }}>
              <SvgIcon
                iconName={'ic24-more'}
                width="12"
                height="10"
                opacity={themeSuit.C23.opacity}
                normalCol={themeSuit.C23.color}
              />
            </View>
          </View>
          <Text
            style={[
              _styles.description,
              { color: themeSuit.C13.color },
              ScreenUtils.isMedium(this.getSize())
                ? { textAlign: 'center' }
                : {},
            ]}
            ellipsizeMode={'tail'}
            numberOfLines={1}
          >
            {cashBack}
          </Text>
        </TouchableOpacity>
        {/* 竖线 */}
        <View
          style={[
            _styles.splitline,
            {
              backgroundColor: themeSuit.C39.color,
              opacity: themeSuit.C39.opacity,
              marginTop: 16,
            },
          ]}
        />
        {this.showMoreMemberInfo(_styles, showMoreMemberInfoParams)}
      </>
    );
  };

  renderGuideVMember = (_styles, theme, isDarkTheme) => {
    const { vproList } = this.props;
    const item = PlatformUtils.isApp()
      ? vproList?.configInfo && JSON.parse(vproList?.configInfo)
      : vproList;
    const guideTitle = item.guideTitle || t('members');
    const guideIcon = isDarkTheme ? item?.guideDarkIcon : item?.guideIcon;
    let openBtnText = item?.openBtnText || '立即开通';
    let isOverlong = false;
    if (openBtnText.length >= 6) {
      openBtnText = openBtnText.substr(0, 6);
      isOverlong = true;
    }
    const themeSuit: any = SuitStyle;
    const showIcon = item?.showGuideSetting === '2' && guideIcon;
    const showText = item?.showGuideSetting === '1' && item?.guide;
    return (
      <TouchableOpacity
        activeOpacity={1}
        style={_styles.guideBg}
        onPress={this.onVProGuideClick}
      >
        <View
          style={[_styles.guideLeftBlock, { paddingTop: showIcon ? 6 : 10 }]}
        >
          <View style={_styles.leftBlock}>
            {showText ? (
              <Text
                style={[
                  _styles.textTitle,
                  {
                    color: themeSuit.C71.color,
                  },
                ]}
              >
                {_.truncate(item.guide, {
                  length: 2,
                  omission: '',
                })}
              </Text>
            ) : null}
            {showIcon ? (
              <FastImageView
                imgUri={guideIcon}
                imgStyle={_styles.logoImg}
                resizeMode={'cover'}
              />
            ) : null}
            <Text
              ellipsizeMode={'clip'}
              numberOfLines={1}
              style={[
                _styles.guideLogoText,
                {
                  color: themeSuit.C71.color,
                  marginLeft: showIcon ? 4 : 0,
                },
              ]}
            >
              {guideTitle}
            </Text>
          </View>
          <Text
            style={[_styles.guideDescription, { color: themeSuit.C13.color }]}
            ellipsizeMode={'tail'}
            numberOfLines={1}
          >
            {item?.guideWords}
          </Text>
        </View>

        <LinearGradient
          style={[_styles.guideRightBlock, { marginTop: showIcon ? 14 : 13.5 }]}
          colors={['#605144', '#1C0A07']}
        >
          <Text
            style={
              isOverlong ? _styles.guideButtonOverlong : _styles.guideButtonText
            }
          >
            {openBtnText}
          </Text>
        </LinearGradient>
      </TouchableOpacity>
    );
  };

  private showMoreMemberInfo(_styles: any, params: any) {
    const {
      showMemberIcon,
      memberUrl,
      showMemberText,
      themeSuit,
      item,
      memberIcon,
    } = params;
    return <TouchableOpacity
      style={[
        ScreenUtils.isMedium(this.getSize())
          ? _styles.padBlock
          : _styles.shopBlock,
        ScreenUtils.isMedium(this.getSize()) && PlatformUtils.isApp()
          ? {}
          : { width: this.getBlockWidth() / 2 },
        {
          paddingTop: showMemberIcon ? 6 : 10,
        },
      ]}
      onPress={() => {
        this.dapReportClickData('12', memberUrl, '12', '1');
        this.handlePress(memberUrl);
      } }
    >
      <View style={_styles.leftBlock}>
        {showMemberText ? (
          <Text
            style={[
              _styles.textTitle,
              {
                color: themeSuit.C71.color,
              },
            ]}
          >
            {_.truncate(item?.memberStore, {
              length: 2,
              omission: '',
            })}
          </Text>
        ) : null}
        {showMemberIcon ? (
          <FastImageView
            imgUri={memberIcon}
            imgStyle={_styles.logoImg}
            resizeMode={'cover'}
            isUser={false} />
        ) : null}
        <Text
          style={[
            _styles.logoTitle,
            {
              color: themeSuit.C71.color,
              marginLeft: item?.showMemberStoreSetting === '2' && memberIcon ? 2 : 0,
            },
          ]}
        >
          {_.truncate(item?.memberStoreTitle, {
            length: 5,
            omission: '',
          })}
        </Text>
        <View style={{ paddingTop: PlatformUtils.isAndroid() || PlatformUtils.isHarmony() ? 1 : 0 }}>
          <SvgIcon
            iconName={'ic24-more'}
            width="12"
            height="10"
            opacity={themeSuit.C23.opacity}
            normalCol={themeSuit.C23.color} />
        </View>
      </View>
      <Text
        style={[
          _styles.shopDescription,
          { color: themeSuit.C13.color },
          ScreenUtils.isMedium(this.getSize())
            ? { textAlign: 'center' }
            : {},
        ]}
        ellipsizeMode={'tail'}
        numberOfLines={1}
      >
        {item?.memberStoreSubTitle}
      </Text>
    </TouchableOpacity>;
  }

  private getOrderIcon(isDarkTheme: any, item: any) {
    return isDarkTheme
      ? item.nOrderCashbackDarkIcon
      : item.nOrderCashbackIcon;
  }

  private getMemberIcon(isDarkTheme: any, item: any) {
    return isDarkTheme
      ? item.memberStoreDarkIcon
      : item.memberStoreIcon;
  }

  private getMemberUrl(item: any) {
    return PlatformUtils.isApp()
      ? item.memberStoreAppLink
      : item.memberStoreWapLink;
  }

  private getCashUrl(item: any) {
    return PlatformUtils.isApp()
      ? item.nOrderCashbackAppLink
      : item.nOrderCashbackWapLink;
  }

  private getItem(vproList: any) {
    return PlatformUtils.isApp()
      ? vproList?.configInfo && JSON.parse(vproList.configInfo)
      : vproList;
  }

  render() {
    const { isMember } = this.props;
    const isDarkTheme = DarkStore.darkBool;
    return (
      <WithTheme themeStyles={Styles}>
        {(_styles, theme) => {
          return (
            <RNImageBackground
              resizeMode="stretch"
              style={[
                ScreenUtils.isMedium(this.getSize()) &&
                PlatformUtils.isApp() &&
                isMember
                  ? _styles.vBgPad
                  : _styles.vBg,
              ]}
              imgUri={
                ScreenUtils.isMedium(this.getSize())
                  ? ImgArray.vgPad
                  : ImgArray.vBg
              }
              localSource={
                ScreenUtils.isMedium(this.getSize())
                  ? ImgArray.vgPad
                  : ImgArray.vBg
              }
              isFromPersonal={true}
            >
              {isMember
                ? this.renderVMember(_styles, theme, isDarkTheme)
                : this.renderGuideVMember(_styles, theme, isDarkTheme)}
            </RNImageBackground>
          );
        }}
      </WithTheme>
    );
  }
}
export { getCardHeight };
export default monitor(dapReportList)(itemExposeHoc(VMember));
