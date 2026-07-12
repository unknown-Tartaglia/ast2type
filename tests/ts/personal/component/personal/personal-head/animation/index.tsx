import { Animated, View, Text, TouchableOpacity } from 'react-native';
import React, { Component } from 'react';
import _ from 'lodash';
import { CommonUtils, PlatformUtils, RecordUtils, t } from '@hw-vmall/vrn-basic-comp';
import { FastImageView } from '@hw-vmall/vrn-bussiness-comp';
import ImgArray from '../../../../../../assets/ImgArray';
import { AnimationHeaderProps } from './props';
const TAG = 'PersonalHead-Title'
export default class AnimationHeader extends Component<AnimationHeaderProps, any> {
  renderHeaderTitle = (_styles: any, titleAnimatedValue: any) => {
    return <Animated.Text style={[_styles.myTitle, { opacity: titleAnimatedValue }]}>{t('service')}</Animated.Text>;
  };

  renderUserName = (_styles, newMergeStyle) => {
    return (
      <Text
        numberOfLines={1}
        style={[
          _styles.userName,
          newMergeStyle?.textStyle?.color && !this.props.isMember ? newMergeStyle.textStyle : null,
          {
            width: PlatformUtils.isApp() ? '100%' : '80%',
            maxWidth: 120,
          },
        ]}
      >
        {this.props.userName}
      </Text>
    );
  };

  // 我的会员标签
  renderMyMember = (_styles: any, isPadH: boolean) => {
    const { userInfoClick, userLevel } = this.props;
    return (
      <TouchableOpacity
        activeOpacity={1}
        style={[
          _styles.tagText,
        ]}
        onPress={() => {
          userInfoClick(t('click_head_to_grade_page'));
        }}
      >
        <FastImageView localSource={ImgArray.medal} imgStyle={_styles.medal} />
        <View style={[_styles.txtBg, isPadH && PlatformUtils.isHarmony() && { paddingTop: 1 * 0.8 }]}>
          <Text
            style={[
              _styles.tagTxt,
            ]}
          >
            V{userLevel}
            {t('grade')}
          </Text>
        </View>
      </TouchableOpacity>
    );
  };

  renderText = (showText: boolean, _styles: any, item: any) => {
    return showText ? (
      <Text style={[_styles.showText]}>
        {_.truncate(item?.avatar, {
          length: 2,
          omission: '',
        })}
      </Text>
    ) : null;
  };

  renderIcon = (showIcon: boolean, avatarIcon: string, _styles: any, item: any) => {
    return showIcon ? (
      <FastImageView
        imgUri={avatarIcon}
        imgStyle={[
          _styles.showIcon,
          {
            marginLeft: item?.avatarIcon !== '' ? 2 : 0,
          },
        ]}
      />
    ) : null;
  };

  renderMember = (
    _styles: any,
    showText: boolean,
    item: any,
    showIcon: boolean,
    avatarIcon: string,
    marginLeft: number,
    defaultAvatar: string,
    newMergeStyle: any,
    userNameAnimateStyle: any,
  ) => {
    const { titleAnimatedValue, userInfoAnimatedValue, userInfoClick, canClick } = this.props;
    return (
      <View
        style={PlatformUtils.isApp() ? _styles.appMemberLoginHeader : _styles.memberLoginHeader}
        pointerEvents={canClick ? 'none' : 'box-none'}
      >
        {this.renderHeaderTitle(_styles, titleAnimatedValue)}
        <Animated.View
          style={[
            _styles.cricle,
            _styles.headerMemberImg,
            {
              transform: [
                {
                  scale: userInfoAnimatedValue,
                },
              ],
              opacity: userInfoAnimatedValue,
            },
          ]}
        >
          <TouchableOpacity
            activeOpacity={1}
            onPress={() => {
              userInfoClick(t('click_head_to_grade_page'));
            }}
            style={{ width: '100%' }}
          >
            <FastImageView localSource={ImgArray.vAvater} imgStyle={_styles.showRadius} isUser={false} />
            <View style={[_styles.showAvatar]}>
              {this.renderText(showText, _styles, item)}
              {this.renderIcon(showIcon, avatarIcon, _styles, item)}
              <Text
                style={[
                  _styles.showText,
                  {
                    marginLeft: marginLeft,
                  },
                ]}
              >
                {t('members')}
              </Text>
            </View>
            <View style={{ width: 32, height: 32 }}>
              <FastImageView
                imgUri={this.props.avaImg}
                localSource={this.props.avaImg ? null : defaultAvatar}
                imgStyle={_styles.avaImg}
                isUser={true}
                onLoadSuccess={() => {
                  this.onLoadResult(true);
                }}
                onError={() => {
                  this.onLoadResult(false);
                }}
              />
            </View>
          </TouchableOpacity>
        </Animated.View>
        <TouchableOpacity
          activeOpacity={1}
          style={_styles.userNameBox}
          onPress={() => {
            userInfoClick(t('click_nickname_to_grade_page'));
          }}
        >
          <Animated.View style={userNameAnimateStyle}>{this.renderUserName(_styles, newMergeStyle)}</Animated.View>
        </TouchableOpacity>
      </View>
    );
  };

  getAnimStyle = (userInfoAnimatedValue) => {
    return {
      transform: [
        {
          translateX: userInfoAnimatedValue?.interpolate({
            inputRange: [0, 1],
            outputRange: [0, 28],
          }),
        },
      ],
      opacity: userInfoAnimatedValue,
    };
  };

  renderLoginHeader = (
    _styles: any,
    showText: boolean,
    item: any,
    showIcon: boolean,
    avatarIcon: string,
    marginLeft: number,
    newMergeStyle: any,
    defaultAvatar: string,
    loginDefaultAvatar: string,
    unLoginDefaultAvatar: string,
    isPadH: boolean,
  ) => {
    const { titleAnimatedValue, userInfoAnimatedValue, userInfoClick, canClick, isMember } = this.props;
    const userNameAnimateStyle = [
      _styles.userNameBoxView,
      this.getAnimStyle(userInfoAnimatedValue),
    ];
    return (
      // 登录账号
      <>
        {isMember ? (
          <>
            {this.renderMember(
              _styles,
              showText,
              item,
              showIcon,
              avatarIcon,
              marginLeft,
              loginDefaultAvatar,
              newMergeStyle,
              userNameAnimateStyle,
            )}
          </>
        ) : (
          <View style={_styles.loginHeader} pointerEvents={canClick ? 'none' : 'box-none'}>
            {this.renderHeaderTitle(_styles, titleAnimatedValue)}
            <Animated.View
              style={[
                {
                  transform: [
                    {
                      scale: userInfoAnimatedValue,
                    },
                  ],
                  opacity: userInfoAnimatedValue,
                },
                _styles.headerImg,
              ]}
            >
              <TouchableOpacity
                activeOpacity={1}
                onPress={() => {
                  userInfoClick(t('click_head_to_grade_page'));
                }}
                style={{ width: '100%' }}
              >
                <FastImageView
                  imgUri={this.props.avaImg}
                  imgStyle={_styles.userAva}
                  localSource={this.props.avaImg ? null : unLoginDefaultAvatar}
                  isUser={true}
                  onError={() => {
                    this.onLoadResult(false);
                  }}
                  onLoadSuccess={() => {
                    this.onLoadResult(true);
                  }}
                />
              </TouchableOpacity>
            </Animated.View>
            <View style={_styles.userNameBox}>
              <Animated.View style={userNameAnimateStyle}>
                <TouchableOpacity
                  activeOpacity={1}
                  onPress={() => {
                    userInfoClick(t('click_nickname_to_grade_page'));
                  }}
                >
                  {this.renderUserName(_styles, newMergeStyle)}
                </TouchableOpacity>
                {this.renderMyMember(_styles, isPadH)}
              </Animated.View>
            </View>
          </View>
        )}
      </>
    );
  };

  onLoadResult = (success: boolean) => {
    const logInfo =  `用户头像加载成功: ${success}。登录状态: ${this.props.isLogin}, 头像地址为空: ${CommonUtils.isEmpty(this.props.avaImg)}` 
    RecordUtils.info(TAG, logInfo);
  }

  renderUnloginHeader = (_styles: any, mergeStyle: any, unLoginText: string, defaultAvatar: string, unLoginDefaultAvatar: string) => {
    const { goLogin, userInfoAnimatedValue, canClick } = this.props;
    return (
      // 未登录
      <View style={_styles.unLoginHeader} pointerEvents={canClick ? 'none' : 'box-none'}>
        {this.renderHeaderTitle(_styles, this.props.titleAnimatedValue)}
        <TouchableOpacity
          activeOpacity={1}
          onPress={() => {
            goLogin(t('click_head_to_grade_page'));
          }}
          style={_styles.headerImg}
        >
          <Animated.View
            style={{
              transform: [
                {
                  scale: userInfoAnimatedValue,
                },
              ],
              opacity: userInfoAnimatedValue,
            }}
          >
            <FastImageView localSource={unLoginDefaultAvatar} isUser={true} imgStyle={_styles.userAva} />
          </Animated.View>
        </TouchableOpacity>
        <TouchableOpacity
          activeOpacity={1}
          onPress={() => {
            goLogin(t('click_nickname_to_grade_page'));
          }}
          style={_styles.userNameBox}
        >
          <Animated.Text
            style={[
              _styles.userName,
              mergeStyle?.textStyle?.color && !this.props.isMember ? mergeStyle.textStyle : null,
              this.getAnimStyle(userInfoAnimatedValue),
            ]}
          >
            {unLoginText}
          </Animated.Text>
        </TouchableOpacity>
      </View>
    );
  };

  render() {
    const {
      _styles,
      mergeStyle,
      unLoginText,
      newMergeStyle,
      isLogin,
      showText,
      item,
      showIcon,
      avatarIcon,
      marginLeft,
      defaultAvatar,
      loginDefaultAvatar,
      unLoginDefaultAvatar,
      isPadH,
    } = this.props;
    return (
      <>
        {isLogin ? (
          <>
            {this.renderLoginHeader(
              _styles,
              showText,
              item,
              showIcon,
              avatarIcon,
              marginLeft,
              newMergeStyle,
              defaultAvatar,
              loginDefaultAvatar,
              unLoginDefaultAvatar,
              isPadH,
            )}
          </>
        ) : (
          <>{this.renderUnloginHeader(_styles, mergeStyle, unLoginText, defaultAvatar, unLoginDefaultAvatar)}</>
        )}
      </>
    );
  }
}
